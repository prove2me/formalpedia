-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_robOf
-- name    : ParetoNCSched_Supplement_robOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:31:30.341184+00:00
-- url     : https://prove2.me/theorems/7fde8b1f-c445-4c45-948a-ac270e613d5c
-- title:
--   Robustness $\mathrm{rob}$
-- statement:
--   For a prediction model and a cost function $(p,y)\mapsto A(p,y)$ (the total completion time of a deterministic algorithm, or the expected total completion time of a randomized one), the **robustness** is
--
--   $$\mathrm{rob}(A)=\sup_{n\ge1}\ \sup_{p\in(0,\infty)^n,\ y}\ \frac{A(p,y)}{\mathrm{OPT}(p)},$$
--
--   the supremum over all numbers of jobs, all sizes and all allowed predictions, where $\mathrm{OPT}(p)$ is the optimal total completion time over all preemptive schedules. An algorithm is $R$-robust if $\mathrm{rob}(A)\le R$.
--
--   **Formalization Note** Values in $[0,\infty]$; $\mathrm{OPT}(p)$ is the base mission's infimum over all schedules, in $(0,\infty)$ for $n\ge1$ and $p>0$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15; Section 2, p.7

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_PredModel
import Definitions.Def_ParetoNCSched_OPT
open scoped ENNReal

namespace ParetoNCSched.Supplement

/-- **Robustness `rob`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15:
"rob(A) = sup_{n≥1} sup_{p∈(0,∞)ⁿ, σ} A(p, σ)/OPT(p)", and "A randomized algorithm … Its
consistency and robustness are defined by the same formulas, with A(p, σ) replaced by its
expectation over the random bits"; Appendix E, p.31: the same with predicted sizes.

`robOf M cost` is the supremum of `cost n p y / OPT(p)` over `n ≥ 1`, sizes `p ∈ (0, ∞)ⁿ` and
every allowed prediction `y` of the model `M`; `cost` is the (expected) total completion time.

**Formalization Note.** Values in `ℝ≥0∞`; `OPT(p)` is the base mission's infimum over all
schedules, which lies in `(0, ∞)` for `n ≥ 1` and `p > 0`, so the quotient is the paper's. -/
noncomputable def robOf (M : PredModel) (cost : (n : ℕ) → (Fin n → ℝ) → M.Pred n → ℝ≥0∞) :
    ℝ≥0∞ :=
  ⨆ (n : ℕ) (_ : 1 ≤ n) (p : Fin n → ℝ) (_ : ∀ j, 0 < p j) (y : M.Pred n) (_ : M.Adm y),
    cost n p y / OPT p

end ParetoNCSched.Supplement


