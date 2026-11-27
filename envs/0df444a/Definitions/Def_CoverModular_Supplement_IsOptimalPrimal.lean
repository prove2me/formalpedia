-- Prove2me | Definitions.Def_CoverModular_Supplement_IsOptimalPrimal
-- name    : CoverModular_Supplement_IsOptimalPrimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:15:57.777001+00:00
-- url     : https://prove2.me/theorems/7b9cde3c-61ee-5f3f-bdfc-cb2d856d93c7
-- title:
--   Optimal solution $x^{\mathcal S}$ of the LP (17)
-- statement:
--   A vector $x\in\mathbb R^n$ is an **optimal solution** of the LP (17) for the set $\mathcal A$ if it is feasible, that is $\sum_ja_{ij}x_j\le b_i$ for all $i$, $x_j=0$ for $j\notin J(\mathcal A)$ and $x\ge0$, and if
--
--   $$
--   \sum_jp_jx_j\ \ge\ \sum_jp_jy_j\qquad\text{for every feasible }y.
--   $$
--
--   In Appendix A.3 of the paper, $x^{\mathcal S}$ denotes an optimal solution of (17) for $\mathcal A=\mathcal S$. It is the primal solution from which the dual vector $\bar\alpha^{\mathcal S}$ is built.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), display (17), p.23; Appendix A.3, p.40

import Mathlib
import Definitions.Def_CoverModular_Supplement_h

namespace CoverModular.Supplement

/-- `x` is an **optimal solution** of the LP (17) for the set `A` (DeValve, Pekeč, Wei, SSRN
3844987, display (17), p.23; "Let x^S be the optimal primal solution", Appendix A.3, p.40):
`x` is feasible and its objective is at least that of every feasible point. -/
def IsOptimalPrimal {U : Type*} [DecidableEq U] {m n : ℕ} (a : Fin m → Fin n → ℕ)
    (p : Fin n → ℝ) (b : Fin m → ℝ) (J : U → Finset (Fin n)) (A : Finset U)
    (x : Fin n → ℝ) : Prop :=
  Feasible a b J A x ∧ ∀ y, Feasible a b J A y → objective p y ≤ objective p x

end CoverModular.Supplement


