-- Prove2me | Definitions.Def_HSElemKernel_HSInstance
-- name    : HSElemKernel_HSInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:22:55.94019+00:00
-- url     : https://prove2.me/theorems/5b8dae38-c1fa-43c7-ba22-c5b270895e18
-- title:
--   Hitting Set instance $(U, \mathcal S, k)$
-- statement:
--   An **instance of Hitting Set** is a triple $(U, \mathcal S, k)$: a finite universe $U$, a family $\mathcal S \subseteq 2^U$ of subsets of $U$, and a nonnegative integer $k$. We write $n = |U|$ and $m = |\mathcal S|$.
--
--   Every object of the mission (codes, kernels, YES-instances, the encodings of Section 4) is defined over such an instance.
--
--   **Formalization Note** The universe is $\{0, \dots, n-1\}$ (`Fin n`); relabelling a finite universe changes no instance. The family is a finite set of finite sets, so each set occurs once, and it may contain the empty set. The bound $|A| \le d$ of $d$-Hitting Set is the separate predicate `IsDHS`.
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 3, p.6 (and Section 1, p.1)

import Mathlib

namespace HSElemKernel

/-- An instance `(U, S, k)` of Hitting Set (Sheng–Xiao, *A Near-Linear Element-Kernel for
d-Hitting Set*, arXiv:2609.06512, held version sha256 aca9c70e…, Section 3, p.6, and Section 1,
p.1): a finite universe `U`, a family `S ⊆ 2^U` of subsets of `U`, and a nonnegative integer `k`.

**Formalization Note** The universe is `Fin n` (`n = |U|`): relabelling a finite universe changes
no instance. `S` is a `Finset` of `Finset`s, so every set occurs at most once, as in `S ⊆ 2^U`; the
empty set may belong to `S`. The size bound `|A| ≤ d` of `d`-Hitting Set is the separate predicate
`IsDHS`. -/
structure HSInstance where
  /-- the number of elements `n = |U|`; the universe is `Fin n` -/
  n : ℕ
  /-- the family `S` of input sets -/
  S : Finset (Finset (Fin n))
  /-- the parameter `k` -/
  k : ℕ

end HSElemKernel


