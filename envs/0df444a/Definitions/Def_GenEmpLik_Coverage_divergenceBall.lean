-- Prove2me | Definitions.Def_GenEmpLik_Coverage_divergenceBall
-- name    : GenEmpLik_Coverage_divergenceBall
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:04:20.230691+00:00
-- url     : https://prove2.me/theorems/c7e52bcf-95dc-44d7-bdec-48eacbb953d5
-- title:
--   Empirical f-divergence ball
-- statement:
--   For $n$ observations and radius $\rho/n$, the empirical divergence ball consists of all nonnegative weights $p$ satisfying
--
--   $$\sum_{i=0}^{n-1}p_i=1,\qquad D_f(p\|\widehat P_n)=\frac1n\sum_{i=0}^{n-1}f(np_i)\le\frac\rho n.$$
--
--   Equivalently, $\sum_i f(np_i)\le\rho$. This is the feasible set underlying the confidence region. The published divergence and probability uncertainty set supply its exact arithmetic.
--
--   **Formalization Note** The definition is meaningful for every natural $n$; the asymptotic claims use positive $n$ eventually.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 12, Eq. (15)

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet

namespace GenEmpLik.Coverage

/-- The empirical f-divergence ball at radius ρ/n, p. 12, (15). -/
def divergenceBall (f : ℝ → EReal) (ρ : ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  PhiDivRobust.Counterpart.probUncertaintySet f (fun _ => (1 : ℝ) / n) (ρ / n)

end GenEmpLik.Coverage


