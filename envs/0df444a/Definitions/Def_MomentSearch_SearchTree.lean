-- Prove2me | Definitions.Def_MomentSearch_SearchTree
-- name    : MomentSearch_SearchTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:36.817931+00:00
-- url     : https://prove2.me/theorems/27bac855-fcd3-4f0a-bc55-1ac7bc86b15e
-- title:
--   Deterministic search strategy on an interval (ordered binary search tree)
-- statement:
--   A **deterministic search strategy** on the path with vertex set $[n]_0=\{0,1,\dots,n-1\}$ searches for an unknown target $t$ by comparison queries: a query at a vertex $v$ reveals whether $t<v$, $t=v$ or $t>v$. Equivalently, a strategy is an **ordered binary search tree**. Each node corresponds to an interval of possible targets $I=\{a,\dots,b\}$ and is labelled by a vertex $v\in I$:
--
--   1. if $a=b$, the target is identified without another query (a leaf);
--   2. otherwise the strategy queries $v$, terminates on equality, and continues on the appropriate nonempty interval $\{a,\dots,v-1\}$ or $\{v+1,\dots,b\}$.
--
--   A strategy on $[n]_0$ is such a tree on the interval $\{0,\dots,n-1\}$. Every strategy must identify every target of $[n]_0$, including targets of probability zero.
--
--   This is the class of strategies over which the optimal cost $\mathrm{OPT}(p)$ and the approximability factor $\alpha$ are taken.
--
--   **Formalization Note** The tree is an inductive family indexed by the interval endpoints $a,b$. A leaf exists only on a singleton interval; a node on $\{a,\dots,b\}$ with $a<b$ has its label in the interval, a left subtree exactly when $\{a,\dots,v-1\}$ is nonempty and a right subtree exactly when $\{v+1,\dots,b\}$ is nonempty. Correctness is therefore built into the type, and a strategy cannot stop while two or more candidates remain. `Strategy n` is the tree on $\{0,\dots,n-1\}$; the paper's standing assumption $n\ge 2$ is a hypothesis of every statement that uses it.
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §2.1, p.5 (PDF p.7)

import Mathlib

namespace MomentSearch

/-- A deterministic comparison-search strategy on the interval `{a, …, b}` of the path, as an
ordered binary search tree (Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §2.1, p.5 (PDF p.7)).

"Each node corresponds to an interval of possible targets I = {a, . . . , b} and is labeled by a
vertex v ∈ I. If a = b, the target is identified without another query. Otherwise, the strategy
queries v, terminates on equality, and continues on the appropriate nonempty interval
{a, . . . , v − 1} or {v + 1, . . . , b}."

* `leaf a` is the singleton interval `{a}`: the target is identified without a query.
* `node v …` is a non-singleton interval `{a, …, b}` (`a < b`) labelled by `v ∈ {a, …, b}`; it
  carries a strategy for `{a, …, v − 1}` exactly when this interval is nonempty (`a < v`), and a
  strategy for `{v + 1, …, b}` exactly when this interval is nonempty (`v < b`).

**Formalization Note.** Correctness is built into the type: a leaf exists only on a singleton
interval, every query vertex lies in its interval and every nonempty side has a subtree, so every
target of `{a, …, b}` is identified, including targets of probability zero. There is no other
constructor; in particular a strategy cannot stop on an interval with two or more candidates. -/
inductive SearchTree : ℕ → ℕ → Type
  | leaf (a : ℕ) : SearchTree a a
  | node {a b : ℕ} (v : ℕ) (hav : a ≤ v) (hvb : v ≤ b) (hab : a < b)
      (left : a < v → SearchTree a (v - 1))
      (right : v < b → SearchTree (v + 1) b) : SearchTree a b

/-- A deterministic search strategy on the path with vertex set `[n]₀ = {0, …, n − 1}`: a search
tree on the whole interval `{0, …, n − 1}` (Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §2.1, p.5 (PDF p.7)).

**Formalization Note.** The paper assumes `n ≥ 2` throughout; every statement using
`Strategy n` carries this hypothesis (for `n = 0` the type would be `SearchTree 0 0`). -/
abbrev Strategy (n : ℕ) : Type := SearchTree 0 (n - 1)

end MomentSearch


