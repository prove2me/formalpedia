-- Prove2me | Definitions.Def_OverbookBL_IsLocOpt
-- name    : OverbookBL_IsLocOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:52:03.164198+00:00
-- url     : https://prove2.me/theorems/55719d46-3165-4695-9ab4-4f079c425143
-- title:
--   Local optimality at type $j$ (Definition 2)
-- statement:
--   Consider problem (1) with capacity $B$, (estimated) future arrivals $\widetilde N^f[t]$ and past accepted arrivals $\vec x[t-1]$. A feasible solution $\vec x^\star$ (that is, $0\le x^\star_n\le\widetilde N^f_n[t]$ for all $n$) is **locally optimal at $j$** if
--
--   $$
--   x^\star_j=\max\ \operatorname*{arg\,max}_{x_j:\,0\le x_j\le \widetilde N^f_j[t]}\Big\{x_jv_j-\mathbb E\Big[\Big(X_{j,x_j[t-1]+x_j}+\sum_{n\ne j}X_{n,x_n[t-1]+x^\star_n}-B\Big)^+\Big]\Big\},
--   $$
--
--   i.e. $x^\star_j$ is the largest optimal number of future type-$j$ customers to accept, given the other coordinates of $\vec x^\star$.
--
--   Local optimality is the condition through which the paper compares solutions: it has the tail characterization of Lemma 1 and the Lipschitz property of Lemma 2.
--
--   **Formalization Note** "Largest maximizer" is stated as: no $y\le\widetilde N^f_j[t]$ does better, and every $y$ with $x^\star_j<y\le\widetilde N^f_j[t]$ does strictly worse. The objective of problem (1) is used in place of the bracket; the two differ by a term that does not depend on $x_j$.
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Definition 2, p.12

import Definitions.Def_OverbookBL_obj

namespace OverbookBL

/-- Local optimality (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2,
Definition 2, p.12). A feasible solution `x` of problem (1) with (estimated) future arrivals
`Nf = Ñᶠ[t]` and past accepted arrivals `past = x⃗[t−1]` is *locally optimal at `j`* if `xⱼ` is
the **largest** maximizer of `y ↦ (objective with `xⱼ` replaced by `y`)` over `0 ≤ y ≤ Ñᶠⱼ[t]`,
the other coordinates being fixed:
`xⱼ = max argmax_{0 ≤ y ≤ Ñᶠⱼ[t]} { y vⱼ − E[(X_{j, pastⱼ + y} + ∑_{n≠j} X_{n, pastₙ + xₙ} − B)⁺] }`.

**Formalization Note** "Largest maximizer" is the pair of conditions: no `y ≤ Ñᶠⱼ` does better,
and every `y` with `xⱼ < y ≤ Ñᶠⱼ` does strictly worse. The objective `obj` of problem (1)
differs from Definition 2's by `∑_{n≠j} vₙ(pastₙ + xₙ) + vⱼ pastⱼ`, which does not depend on
`y`, so the argmax is the same. Feasibility `x ≤ Ñᶠ[t]` (coordinatewise; `x ≥ 0` is automatic in
`ℕ`) is part of the definition ("Consider a feasible solution"). -/
def IsLocOpt {k : ℕ} (I : Instance k) (B : ℕ) (past Nf x : Fin k → ℕ) (j : Fin k) : Prop :=
  x ≤ Nf ∧
  (∀ y : ℕ, y ≤ Nf j → obj I B past (Function.update x j y) ≤ obj I B past x) ∧
  (∀ y : ℕ, x j < y → y ≤ Nf j → obj I B past (Function.update x j y) < obj I B past x)

end OverbookBL


