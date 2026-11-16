-- Prove2me | Definitions.Def_ParetoNCSched_Supplement_Rstar
-- name    : ParetoNCSched_Supplement_Rstar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:32:45.559924+00:00
-- url     : https://prove2.me/theorems/b4f52968-7551-4a81-bacf-e4b343ffc3c4
-- title:
--   The deterministic frontier $R^*(c_0)$
-- statement:
--   For $c_0\ge1$, $R^*(c_0)$ is the infimum of $\mathrm{rob}(A)$ over the deterministic algorithms $A$ with $\mathrm{cons}(A)\le c_0$, in either prediction model:
--
--   $$R^*(c_0)=\inf\{\mathrm{rob}(A): A\text{ deterministic, with predicted orders or with predicted sizes},\ \mathrm{cons}(A)\le c_0\}.$$
--
--   It is the smallest robustness a deterministic algorithm can have at consistency $c_0$; by Theorems 1.1 and E.2 the frontier is the curve $\{(c(R),R):R>2\}$.
--
--   **Formalization Note** One infimum over the union of the two classes of algorithms, in $[0,\infty]$ (an empty infimum is $\infty$).
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix F, p.36; Section 1.1, p.4

import Mathlib
import Definitions.Def_ParetoNCSched_Supplement_algCost
import Definitions.Def_ParetoNCSched_Supplement_robOf
import Definitions.Def_ParetoNCSched_Supplement_consOf
import Definitions.Def_ParetoNCSched_Supplement_orderModel
import Definitions.Def_ParetoNCSched_Supplement_sizeModel
open scoped ENNReal

namespace ParetoNCSched.Supplement

/-- **The deterministic frontier `R*(c₀)`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix F, p.36: "For c0 ≥ 1, let R∗(c0) be
the infimum of rob(A) over the deterministic algorithms A with cons(A) ≤ c0, in either prediction
model" (also Section 1.1, p.4: "the smallest robustness of a deterministic algorithm with
consistency c0").

One infimum over the union of the deterministic algorithms with predicted orders and those with
predicted sizes, in `ℝ≥0∞` (an empty infimum is `⊤`).

**Formalization Note.** `c₀` is taken in `ℝ≥0∞`; the paper uses `c₀ ≥ 1` only. -/
noncomputable def Rstar (c₀ : ℝ≥0∞) : ℝ≥0∞ :=
  (⨅ (A : DetAlg orderModel) (_ : consOf orderModel (fun _ p σ => algCost A p σ) ≤ c₀),
      robOf orderModel (fun _ p σ => algCost A p σ)) ⊓
    (⨅ (A : DetAlg sizeModel) (_ : consOf sizeModel (fun _ p y => algCost A p y) ≤ c₀),
      robOf sizeModel (fun _ p y => algCost A p y))

end ParetoNCSched.Supplement


