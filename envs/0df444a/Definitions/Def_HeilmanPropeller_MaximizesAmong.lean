-- Prove2me | Definitions.Def_HeilmanPropeller_MaximizesAmong
-- name    : HeilmanPropeller_MaximizesAmong
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:38.721962+00:00
-- url     : https://prove2.me/theorems/367ffcd3-9010-4aa0-a8c0-0ff253c9ccb8
-- title:
--   A partition into $k\le N$ sets maximizing $F$ among $N$-set partitions
-- statement:
--   Fix $n$ and $N$. A partition $\mathcal A=(A_1,\dots,A_k)$ of $\mathbb R^n$ into $k$ measurable sets **maximizes $F$ among partitions of $\mathbb R^n$ into $N$ sets** when $k\le N$ and
--
--   $$F(\mathcal B)\le F(\mathcal A)\quad\text{for every partition }\mathcal B\text{ of }\mathbb R^n\text{ into }N\text{ sets},$$
--
--   where $F(\mathcal A)=\sum_i\|\int_{A_i}x\,d\gamma_n(x)\|^2$. This is the maximizing partition of Lemma 2.1 of the paper. A partition into $k\le N$ sets is also one into $N$ sets after appending empty cells.
--
--   **Formalization Note** Partitions are almost-everywhere partitions (`IsPartition` of the reused block `OAI.GaussianPropeller`); a null modification changes no moment, so the maximum is the same as over exact partitions.
-- source:
--   Heilman, On the Propeller Conjecture, arXiv:2610.32158 (held version, sha256 13f5ddf8…), Lemma 2.1, p.4

import Mathlib
import Definitions.Def_GaussianPropeller

namespace HeilmanPropeller

open OAI.GaussianPropeller

/-- **A maximizing partition into at most `N` sets.** Heilman, *On the Propeller Conjecture*,
arXiv:2610.32158 (held version, sha256 13f5ddf8…), Lemma 2.1, p.4: "a measurable partition
`A ⊆ ℝⁿ` into `k ≤ N` sets maximizing `F(A)` among partitions of `ℝⁿ` into `N` sets".

`MaximizesAmong N A` holds for `A = (A₁, …, A_k)` with `k ≤ N` when `A` is a partition of `ℝⁿ` and
`F(A) ≥ F(B)` for every partition `B` of `ℝⁿ` into `N` sets.

**Formalization Note.**
* Partitions are `IsPartition` (measurable cells, `γₙ`-a.e. point in exactly one cell), from the
  reused block `OAI.GaussianPropeller`. A null modification changes no moment, so the maximum over
  these equals the paper's maximum over exact partitions.
* A partition into `k ≤ N` sets is also one into `N` sets after appending empty cells, which is why
  `A` is compared with `N`-cell partitions only. -/
def MaximizesAmong {n k : ℕ} (N : ℕ) (A : Fin k → Set (Space n)) : Prop :=
  IsPartition A ∧ k ≤ N ∧ ∀ B : Fin N → Set (Space n), IsPartition B → value B ≤ value A

end HeilmanPropeller


