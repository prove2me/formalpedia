-- Prove2me | Definitions.Def_ParetoIneff_Mech_IsComponents
-- name    : ParetoIneff_Mech_IsComponents
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:51.746359+00:00
-- url     : https://prove2.me/theorems/c9c6f942-2fc2-4816-9afc-d9eef3e00fec
-- title:
--   Components of a task-independent mechanism
-- statement:
--   Single-task mechanisms $\mathcal A_j=(y^j,q^j)$, $j=1,\dots,m$, are **components** of the $m$-task part of $\mathcal M=(x,p)$ if, for every task $j$, every machine $i$ and every strategy profile $s$,
--   $$
--   x^j(s)=y^j(s^j)\qquad\text{and}\qquad p_i(s)=\sum_{j=1}^m q_i^j(s^j).
--   $$
--   So each task is allocated from its own column of reports alone, and a machine's payment is the sum of its payments per task. This is the formal content of task-independence (Definition 1).
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, Definition 1, p.6

import Mathlib
import Definitions.Def_ParetoIneff_Mech
import Definitions.Def_ParetoIneff_SingleTaskMech
import Definitions.Def_ParetoIneff_col

open NNReal

namespace ParetoIneff

/-- The single-task mechanisms `{𝒜_j}_{j=1,…,m}` are **components** of the `m`-task part of `ℳ`,
Definition 1 (Task-independence), arXiv:1809.03454v7, p.6: for every task `j`, every machine `i`
and every reported profile `s`,
`xʲ(s) = yʲ(sʲ)` and `pᵢ(s) = ∑_{j=1}^m q_iʲ(sʲ)`,
where `sʲ` is the `j`-th column of `s`. -/
def Mech.IsComponents {n : ℕ} (M : Mech n) (m : ℕ) (A : Fin m → SingleTaskMech n) : Prop :=
  ∀ s : Fin n → Fin m → ℝ≥0,
    (∀ j : Fin m, M.alloc m s j = (A j).alloc (col s j)) ∧
    (∀ i : Fin n, M.pay m s i = ∑ j : Fin m, (A j).pay (col s j) i)

end ParetoIneff


