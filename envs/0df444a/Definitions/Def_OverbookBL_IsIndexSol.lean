-- Prove2me | Definitions.Def_OverbookBL_IsIndexSol
-- name    : OverbookBL_IsIndexSol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:40.854765+00:00
-- url     : https://prove2.me/theorems/645bf43f-a0b2-4516-8c27-dfdeb6c3894b
-- title:
--   Index solution and its (smallest) threshold index (Definition 1)
-- statement:
--   Suppose the remaining arrivals in period $t$ are estimated to be $\widetilde N^f[t]$. A feasible vector $\vec x$ ($0\le x_j\le\widetilde N^f_j[t]$) is an **index solution with threshold index $\tilde\jmath\in[k]$** if
--
--   $$
--   x_j=\widetilde N^f_j[t]\ \text{ for all } j<\tilde\jmath,\qquad x_j=0\ \text{ for all } j>\tilde\jmath .
--   $$
--
--   When several indices qualify, the threshold index is the smallest one; this implies $x_{\tilde\jmath}>0$ unless $\vec x=0$.
--
--   Index solutions fill types in order of critical ratio, like the greedy solution of a knapsack LP; the online policy and the clairvoyant index benchmarks optimize over them.
--
--   **Formalization Note** `IsIndexSol Nf x e` says $e$ is a threshold index; `IsThreshold Nf x e` says it is the smallest one.
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Definition 1, p.10

import Mathlib

namespace OverbookBL

/-- Index solutions (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2,
Definition 1, p.10). A feasible vector `x ≤ Nf` of problem (1) with estimated future arrivals
`Nf = Ñᶠ[t]` is an *index solution with threshold index `e`* if every future arrival of a type
`j < e` is accepted (`xⱼ = Ñᶠⱼ[t]`) and none of a type `j > e` is (`xⱼ = 0`).

**Formalization Note** Types are `Fin k` in the paper's order. Whether `x` is an index solution
does not depend on the past accepted arrivals. -/
def IsIndexSol {k : ℕ} (Nf x : Fin k → ℕ) (e : Fin k) : Prop :=
  x ≤ Nf ∧ (∀ j, j < e → x j = Nf j) ∧ (∀ j, e < j → x j = 0)

/-- The threshold index of an index solution (arXiv:2204.11148v2, Definition 1, p.10, "when more
than one index could be a threshold index, we uniquely define `j̃` to be the smallest possible
one"): `e` is a threshold index of `x` and no smaller index is. -/
def IsThreshold {k : ℕ} (Nf x : Fin k → ℕ) (e : Fin k) : Prop :=
  IsIndexSol Nf x e ∧ ∀ e', e' < e → ¬ IsIndexSol Nf x e'

end OverbookBL


