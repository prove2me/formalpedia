-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_consOf
-- name    : ParetoNCSched_Supplement_consOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:32:02.264838+00:00
-- url     : https://prove2.me/theorems/6cd94b1a-8a11-414a-ae4e-0cda96b7de1e
-- title:
--   Consistency $\mathrm{cons}$
-- statement:
--   For a prediction model and a cost function $(p,y)\mapsto A(p,y)$, the **consistency** is
--
--   $$\mathrm{cons}(A)=\sup_{n\ge1}\ \sup_{p\in(0,\infty)^n,\ y\text{ correct for }p}\ \frac{A(p,y)}{\mathrm{OPT}(p)},$$
--
--   the same supremum restricted to correct predictions. An algorithm is $c$-consistent if $\mathrm{cons}(A)\le c$.
--
--   **Formalization Note** Values in $[0,\infty]$, as for $\mathrm{rob}$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15; Section 2, p.7

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_PredModel
import Definitions.Def_ParetoNCSched_OPT
open scoped ENNReal

namespace ParetoNCSched.Supplement

/-- **Consistency `cons`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix A, Model, p.15:
"cons(A) = sup_{n≥1} sup_{p∈(0,∞)ⁿ, σ correct for p} A(p, σ)/OPT(p)", with the expectation for a
randomized algorithm; Appendix E, p.31: the same with predicted sizes.

`consOf M cost` is the supremum of `cost n p y / OPT(p)` over `n ≥ 1`, `p ∈ (0, ∞)ⁿ` and every
allowed prediction `y` of `M` that is correct for `p`.

**Formalization Note.** Values in `ℝ≥0∞`, as for `robOf`. -/
noncomputable def consOf (M : PredModel) (cost : (n : ℕ) → (Fin n → ℝ) → M.Pred n → ℝ≥0∞) :
    ℝ≥0∞ :=
  ⨆ (n : ℕ) (_ : 1 ≤ n) (p : Fin n → ℝ) (_ : ∀ j, 0 < p j) (y : M.Pred n) (_ : M.Adm y)
    (_ : M.Correct p y), cost n p y / OPT p

end ParetoNCSched.Supplement


