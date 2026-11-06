-- Prove2me | Definitions.Def_TreeMultiflow_lpOpt
-- name    : TreeMultiflow_lpOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:15.385242+00:00
-- url     : https://prove2.me/theorems/9deff879-a877-4d17-8cc8-d7f56a214513
-- title:
--   Fractional optimum of LP (1)
-- statement:
--   For nonnegative weights $w$, the **fractional optimum** is
--   $$
--   \mathrm{LP}^*=\sup\Bigl\{\sum_{f\in F} w_f x_f : x \text{ a feasible solution of (1)}\Bigr\}.
--   $$
--
--   The integrality gap compares this value with the integral optimum.
--
--   **Formalization Note** The set is nonempty ($x=0$) and bounded above by $\sum_f|w_f|$, so the real supremum is the LP optimum.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Section 1, p.2 (LP (1); the fractional optimum)

import Mathlib
import Definitions.Def_TreeMultiflow_IsLPFeasible

namespace TreeMultiflow

/-- **Fractional optimum of LP (1).**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Section 1,
p.2: "maximize Σ_{f∈F} w_f x_f" subject to (1); "the fractional optimum".

`lpOpt G u src dst w` is the supremum of `Σ_f w f * x f` over the feasible solutions `x` of (1).

**Formalization Note.** The set of values is nonempty (`x = 0` is feasible) and bounded above by
`Σ_f |w f|` (since `0 ≤ x ≤ 1`), so the real `sSup` is the LP optimum (it is attained, but this is
not used in the definition). -/
noncomputable def lpOpt {V F : Type*} [Fintype F] (G : SimpleGraph V) (u : Sym2 V → ℕ)
    (src dst : F → V) (w : F → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ x : F → ℝ, IsLPFeasible G u src dst x ∧ v = ∑ f, w f * x f}

end TreeMultiflow


