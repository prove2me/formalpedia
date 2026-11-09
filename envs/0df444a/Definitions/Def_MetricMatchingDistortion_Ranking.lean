-- Prove2me | Definitions.Def_MetricMatchingDistortion_Ranking
-- name    : MetricMatchingDistortion_Ranking
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:43.251795+00:00
-- url     : https://prove2.me/theorems/0820b2d9-b483-4849-91f4-71f061095a3c
-- title:
--   Ordinal matching instance: rankings of $n$ items by $n$ agents, $\mathrm{Top}(a,s)$
-- statement:
--   A **matching instance** with $n\ge 1$ agents and $n$ items has agents $A=\{0,\dots,n-1\}$, items $B=\{0,\dots,n-1\}$, and for each agent $a$ a strict total order $\succ_a$ on the items. It is encoded by the rank bijections $r_a:B\to\{0,\dots,n-1\}$, $r_a(b)$ being the position of $b$ in $a$'s list ($0$ for the favorite item):
--   $$b\succ_a b'\iff r_a(b)<r_a(b').$$
--   For $s\ge 0$, $\mathrm{Top}(a,s)=\{b: r_a(b)<s\}$ is the set of the first $s$ items in $a$'s ranking.
--
--   These are the ordinal data a matching mechanism sees.
--
--   **Formalization Note** Agents and items are `Fin n`; every instance with $|A|=|B|=n$ is a relabelling of one of these.
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), §2, p.9 (PDF p.11); §3.2, p.15 (PDF p.17)

import Mathlib

namespace MetricMatchingDistortion

/-- **Ordinal matching instance.** Charikar et al., *Sublinear Metric Distortion for Matching*,
arXiv:2611.05777 (held version, sha256 fdf3452b…), §2, p.9 (PDF p.11): "A matching instance is a
tuple σ = (A, B, {≻a}a∈A), where A is a set of agents, B is a set of items, and for each agent
a ∈ A, ≻a is a total linear order over the items. … All instances will have |A| = |B| = n for some
n ≥ 1".

Agents and items are both `Fin n`. A ranking profile `rk` gives, for each agent `a`, a bijection
`rk a : Fin n ≃ Fin n` sending an item to its position in `a`'s list (position `0` is `a`'s
favorite item). Agent `a` prefers `b` to `b'` (`b ≻_a b'`) iff `rk a b < rk a b'`.

**Formalization Note.** Every instance with `|A| = |B| = n` is a relabelling of one of these, and
a strict total order on `n` items is the same as its rank bijection. -/
abbrev Ranking (n : ℕ) := Fin n → (Fin n ≃ Fin n)

/-- `b ≻_a b'`: agent `a` ranks item `b` strictly above item `b'` (§2, p.9). -/
def Prefers {n : ℕ} (rk : Ranking n) (a b b' : Fin n) : Prop := rk a b < rk a b'

/-- `Top(a, s)`: the first `s` items in agent `a`'s ranking (§3.2, p.15 = PDF p.17: "Let Top(a, s)
denote the first s items in agent a's ranking in σ"). For `s ≥ n` it is the set of all items. -/
def Top {n : ℕ} (rk : Ranking n) (a : Fin n) (s : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun b => ((rk a b : Fin n) : ℕ) < s

end MetricMatchingDistortion


