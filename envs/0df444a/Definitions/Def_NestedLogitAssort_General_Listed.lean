-- Prove2me | Definitions.Def_NestedLogitAssort_General_Listed
-- name    : NestedLogitAssort_General_Listed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:45:22.903846+00:00
-- url     : https://prove2.me/theorems/1b886e93-3145-44c9-af03-08caa488cd21
-- title:
--   Index range of the expression (12)
-- statement:
--   A nest $i$ is fully captured when $v_{i0}=0$ (the set $M^f$) and partially captured when $v_{i0}>0$ (the set $M^p$). The expression (12) takes ratios $V_i(N_{ij})/V_i(N_{i,j-1})$ over the pairs
--
--   1. $i\in M^f$ and $j=2,\dots,n$;
--   2. $i\in M^p$ and $j=1,\dots,n$.
--
--   This predicate says that $(i,j)$ is one of these pairs. For a fully-captured nest the term $j=1$ is left out because $V_i(N_{i0})=V_i(\emptyset)=0$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, eq. (12), p. 26; fully/partially captured nests p. 9

import Mathlib
import Definitions.Def_NestedLogitAssort_General_Instance

namespace NestedLogitAssort.General

/-- **The index pairs of the expression (12).**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, eq. (12), p. 26: the maximum in (12) runs over `i ∈ M^f`, `j = 2, …, n` and over
`i ∈ M^p`, `j = 1, …, n`, where `M^f` (fully-captured nests, `v_{i0} = 0`) and `M^p`
(partially-captured nests, `v_{i0} > 0`) are defined on pp. 9 and 26.

**Formalization Note.** `j` is the paper's 1-based product count. For nonnegative `v_{i0}` the two
cases partition the nests. -/
def Listed {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (j : ℕ) : Prop :=
  (I.w0 i = 0 ∧ 2 ≤ j ∧ j ≤ n) ∨ (0 < I.w0 i ∧ 1 ≤ j ∧ j ≤ n)

end NestedLogitAssort.General


