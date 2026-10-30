-- Prove2me | Definitions.Def_NestedLogitAssort_General_R
-- name    : NestedLogitAssort_General_R
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:39:17.559366+00:00
-- url     : https://prove2.me/theorems/ddbf8864-68f4-4da1-92f8-c90e7b310841
-- title:
--   Expected revenue $R_i(S_i)$ from a nest
-- statement:
--   For a nest $i$ and an assortment $S\subseteq N$, the expected revenue obtained from nest $i$ given that the customer chooses this nest is
--
--   $$
--   R_i(S)=\frac{\sum_{j\in S}r_{ij}v_{ij}}{V_i(S)},
--   $$
--
--   with the interpretation $R_i(\emptyset)=0$.
--
--   **Formalization Note** Division by zero returns $0$ in Lean. With nonnegative weights $V_i(S)=0$ forces the numerator to vanish, so $R_i(S)=0$ there, which realizes the paper's convention $R_i(\emptyset)=0$ when $v_{i0}=0$.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 1, p. 7

import Mathlib
import Definitions.Def_NestedLogitAssort_General_V

namespace NestedLogitAssort.General

/-- **Expected revenue `R_i(S_i)` from a nest.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 1, p. 7 (unnumbered):
`R_i(S_i) = (∑_{j ∈ S_i} r_{ij} v_{ij}) / V_i(S_i)`, "with the interpretation that `R_i(∅) = 0`".

**Formalization Note.** Lean's division gives `a / 0 = 0`. With nonnegative weights,
`V_i(S_i) = 0` forces the numerator to be `0`, so the value is `0` there, which realizes the
paper's convention `R_i(∅) = 0` when `v_{i0} = 0` (and `R_i(∅) = 0 / v_{i0} = 0` otherwise). -/
noncomputable def R {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (S : Finset (Fin n)) : ℝ :=
  (∑ j ∈ S, I.r i j * I.v i j) / V I i S

end NestedLogitAssort.General


