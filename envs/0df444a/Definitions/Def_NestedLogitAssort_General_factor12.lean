-- Prove2me | Definitions.Def_NestedLogitAssort_General_factor12
-- name    : NestedLogitAssort_General_factor12
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:46:08.796767+00:00
-- url     : https://prove2.me/theorems/ba28349d-6c96-404f-8590-454ca7e9df8a
-- title:
--   Performance guarantee $\beta$ of expression (12)
-- statement:
--   Write $a\vee b=\max\{a,b\}$. The performance guarantee of Section 6.1 is
--
--   $$
--   \beta=\max_{i\in M^f,\,j=2,\dots,n}\left\{\frac{V_i(N_{ij})}{V_i(N_{i,j-1})}\right\}\ \vee\ \max_{i\in M^p,\,j=1,\dots,n}\left\{\frac{V_i(N_{ij})}{V_i(N_{i,j-1})}\right\}\ \vee\ 2,
--   $$
--
--   the largest of $2$ and of the ratios of consecutive nested-by-revenue preference weights over the listed pairs. For example, if the largest and the smallest preference weights within a nest differ by at most a factor $\kappa$, then $\beta\le2\kappa$.
--
--   **Formalization Note** A finite maximum (`Finset.max'`), never a real supremum. Lean returns $0$ for a division by zero; the theorems that use $\beta$ assume that every denominator $V_i(N_{i,j-1})$ of a listed pair is positive, which is where (12) is defined.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, eq. (12), p. 26

import Mathlib
import Definitions.Def_NestedLogitAssort_General_V
import Definitions.Def_NestedLogitAssort_General_NBR
import Definitions.Def_NestedLogitAssort_General_Listed

namespace NestedLogitAssort.General

open Classical in
/-- **The performance guarantee `β`, expression (12).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, eq. (12), p. 26:
`max_{i ∈ M^f, j = 2,…,n} {V_i(N_{ij}) / V_i(N_{i,j−1})} ∨ max_{i ∈ M^p, j = 1,…,n} {V_i(N_{ij}) / V_i(N_{i,j−1})} ∨ 2`,
where `a ∨ b = max {a, b}`; "if `i` is a fully-captured nest, then `V_i(N_{i0}) = V_i(∅) = 0` and
we do not consider the term `V_i(N_{i1})/V_i(N_{i0})`".

`factor12 I` is the largest element of the finite set consisting of `2` and the ratios
`V_i(N_{ij}) / V_i(N_{i,j−1})` over the pairs `(i, j)` with `Listed I i j`.

**Formalization Note.** A finite maximum (`Finset.max'`), never a real supremum. Lean's
`a / 0 = 0` would give a zero denominator the value `0`; the theorems using `factor12` assume the
denominators are positive, which is where (12) is defined. `j - 1` is natural subtraction, used
only for `j ≥ 1`. -/
noncomputable def factor12 {M : Type*} [Fintype M] {n : ℕ} (I : Instance M n) : ℝ :=
  (insert 2 (((Finset.univ ×ˢ Finset.range (n + 1)).filter (fun p : M × ℕ => Listed I p.1 p.2)).image
    (fun p => V I p.1 (NBR n p.2) / V I p.1 (NBR n (p.2 - 1))))).max' (Finset.insert_nonempty _ _)

end NestedLogitAssort.General


